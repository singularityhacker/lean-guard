import os

def main():
    key = os.environ.get("DEMO_API_KEY")
    print("configured" if key else "missing key")

if __name__ == "__main__":
    main()
